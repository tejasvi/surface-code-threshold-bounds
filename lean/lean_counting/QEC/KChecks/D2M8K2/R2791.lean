import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11164 = true := by
  decide +kernel

theorem tot11164 : totK PD2M8K2 D2M8K2.t11164 = [0, 196018273815, 481963989997, 221145063803, 12399358509, 0, 0, 0] := by
  decide +kernel

theorem rows11165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11165 = true := by
  decide +kernel

theorem tot11165 : totK PD2M8K2 D2M8K2.t11165 = [0, 0, 284735963009, 487973950761, 131454526678, 4002076922, 0, 0] := by
  decide +kernel

theorem rows11166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11166 = true := by
  decide +kernel

theorem tot11166 : totK PD2M8K2 D2M8K2.t11166 = [0, 106517104648, 353151504964, 355228880318, 84413610476, 1346730670, 0, 0] := by
  decide +kernel

theorem rows11167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11167 = true := by
  decide +kernel

theorem tot11167 : totK PD2M8K2 D2M8K2.t11167 = [0, 168712398140, 443637150338, 279161871416, 27769650833, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
