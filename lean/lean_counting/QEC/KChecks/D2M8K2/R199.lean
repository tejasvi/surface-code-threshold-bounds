import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t796 = true := by
  decide +kernel

theorem tot796 : totK PD2M8K2 D2M8K2.t796 = [0, 34532533563, 323353079454, 444750830616, 96732040504, 1178074134, 0, 0] := by
  decide +kernel

theorem rows797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t797 = true := by
  decide +kernel

theorem tot797 : totK PD2M8K2 D2M8K2.t797 = [0, 0, 194384044491, 475110260825, 192507949581, 12005010568, 0, 0] := by
  decide +kernel

theorem rows798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t798 = true := by
  decide +kernel

theorem tot798 : totK PD2M8K2 D2M8K2.t798 = [0, 154859096135, 433252638030, 287032590038, 34950771162, 0, 0, 0] := by
  decide +kernel

theorem rows799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t799 = true := by
  decide +kernel

theorem tot799 : totK PD2M8K2 D2M8K2.t799 = [0, 189877190717, 451210856922, 234292266976, 21584243628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
