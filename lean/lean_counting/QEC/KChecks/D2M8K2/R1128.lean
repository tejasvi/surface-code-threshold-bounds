import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4512 = true := by
  decide +kernel

theorem tot4512 : totK PD2M8K2 D2M8K2.t4512 = [0, 0, 247136965138, 510447796484, 135004228635, 2309606161, 0, 0] := by
  decide +kernel

theorem rows4513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4513 = true := by
  decide +kernel

theorem tot4513 : totK PD2M8K2 D2M8K2.t4513 = [0, 67204494367, 275702409218, 384400805927, 148424053087, 10734177179, 0, 0] := by
  decide +kernel

theorem rows4514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4514 = true := by
  decide +kernel

theorem tot4514 : totK PD2M8K2 D2M8K2.t4514 = [0, 173966681360, 462407066395, 269781036803, 24354946270, 0, 0, 0] := by
  decide +kernel

theorem rows4515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4515 = true := by
  decide +kernel

theorem tot4515 : totK PD2M8K2 D2M8K2.t4515 = [0, 89127899462, 356457306646, 385596740909, 76015890615, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
