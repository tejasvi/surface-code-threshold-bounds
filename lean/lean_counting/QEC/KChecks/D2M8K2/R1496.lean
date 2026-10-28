import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5984 = true := by
  decide +kernel

theorem tot5984 : totK PD2M8K2 D2M8K2.t5984 = [0, 0, 181029389586, 466166419632, 253585136059, 21890168488, 0, 0] := by
  decide +kernel

theorem rows5985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5985 = true := by
  decide +kernel

theorem tot5985 : totK PD2M8K2 D2M8K2.t5985 = [0, 0, 168812969868, 462119516077, 238357874455, 10291575752, 0, 0] := by
  decide +kernel

theorem rows5986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5986 = true := by
  decide +kernel

theorem tot5986 : totK PD2M8K2 D2M8K2.t5986 = [0, 0, 0, 274812982580, 477888937661, 119601177306, 3962658158, 0] := by
  decide +kernel

theorem rows5987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5987 = true := by
  decide +kernel

theorem tot5987 : totK PD2M8K2 D2M8K2.t5987 = [0, 0, 101353593170, 337623828208, 348885519476, 71866221935, 1163853884, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
