import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15408 = true := by
  decide +kernel

theorem tot15408 : totK PD2M8K2 D2M8K2.t15408 = [0, 193740552423, 458089794312, 243766790999, 19619063205, 0, 0, 0] := by
  decide +kernel

theorem rows15409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15409 = true := by
  decide +kernel

theorem tot15409 : totK PD2M8K2 D2M8K2.t15409 = [0, 141679859810, 451460674382, 286399873191, 27515036418, 0, 0, 0] := by
  decide +kernel

theorem rows15410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15410 = true := by
  decide +kernel

theorem tot15410 : totK PD2M8K2 D2M8K2.t15410 = [0, 0, 180833252911, 445501161542, 257274413682, 25364689049, 0, 0] := by
  decide +kernel

theorem rows15411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15411 = true := by
  decide +kernel

theorem tot15411 : totK PD2M8K2 D2M8K2.t15411 = [0, 0, 209053435211, 491471024813, 188767732369, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
