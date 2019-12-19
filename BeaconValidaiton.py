def main():
    print("Hello world")
    beacons = {}
    beacons_rev = {}
    respCodes = {}
    respCodes_rev = {}

    with open(r"C:\Users\shanil.jain.ECHOSTAR\Desktop\FiringBeacon.txt","r") as firingbeacon:
        line = firingbeacon.readline()
        cnt = 1
        while line:
            k = line[0:26].strip()
            v = line.split("url :")[1].strip()
            line = firingbeacon.readline()
            beacons[k] = v
            beacons_rev[v] = k
            cnt += 1
    print(beacons.values())
    firingbeacon.close()
    with open(r"C:\Users\shanil.jain.ECHOSTAR\Desktop\ResponseCode.txt","r") as responseCode:
        line2 = responseCode.readline()
        cnt2 = 1
        while line2:
            k2 = line2[0:26].strip()
            v2 = line2.split("url:")[1].strip()
            line2 = responseCode.readline()
            respCodes[k2] = v2
            respCodes_rev[v2] = k2
            cnt2 += 1
    print(respCodes.values())
    responseCode.close()
    print(len(beacons))
    print(len(respCodes))
    matchcnt = 0
    rcount = 1
    icount = 1
    foundflag=0
    for keys,vals in beacons.items():
        for logtime,beaconurl in respCodes.items():
            if vals == beaconurl:
                foundflag = 1
                matchcnt += 1
                beacons[keys] = "MATCHED"
                respCodes[logtime] = "MATCHED"
                # print(keys + "--->" + logtime + "  " + vals)
                print(str(icount) + " -- " + str(rcount))
                break
            rcount += 1
        if foundflag == 0:
            print(str(icount) + "NOT FOUND" + "--" + vals)
        icount += 1
        rcount = 1
        foundflag=0
    print(matchcnt)
    print(respCodes.values())
    print(beacons.values())


if __name__ == '__main__':
    main()


