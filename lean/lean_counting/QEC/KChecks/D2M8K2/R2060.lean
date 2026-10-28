import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8240 = true := by
  decide +kernel

theorem tot8240 : totK PD2M8K2 D2M8K2.t8240 = [0, 0, 279302742272, 469964015033, 109184632580, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8241 = true := by
  decide +kernel

theorem tot8241 : totK PD2M8K2 D2M8K2.t8241 = [0, 105497177992, 415644873362, 323939285141, 33591495300, 0, 0, 0] := by
  decide +kernel

theorem rows8242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8242 = true := by
  decide +kernel

theorem tot8242 : totK PD2M8K2 D2M8K2.t8242 = [0, 200180274145, 451977759158, 206318693585, 12552144954, 0, 0, 0] := by
  decide +kernel

theorem rows8243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8243 = true := by
  decide +kernel

theorem tot8243 : totK PD2M8K2 D2M8K2.t8243 = [0, 177034504684, 472165731444, 218409505729, 12593797338, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
