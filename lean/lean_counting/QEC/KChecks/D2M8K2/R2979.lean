import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11916 = true := by
  decide +kernel

theorem tot11916 : totK PD2M8K2 D2M8K2.t11916 = [0, 145614629867, 457345543780, 285307955638, 24745883321, 0, 0, 0] := by
  decide +kernel

theorem rows11917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11917 = true := by
  decide +kernel

theorem tot11917 : totK PD2M8K2 D2M8K2.t11917 = [0, 0, 178147907570, 442281199191, 251090679835, 25191558099, 0, 0] := by
  decide +kernel

theorem rows11918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11918 = true := by
  decide +kernel

theorem tot11918 : totK PD2M8K2 D2M8K2.t11918 = [0, 0, 215632973039, 489677863044, 176151266482, 5206224793, 0, 0] := by
  decide +kernel

theorem rows11919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11919 = true := by
  decide +kernel

theorem tot11919 : totK PD2M8K2 D2M8K2.t11919 = [0, 170815217169, 346837941747, 286019061789, 109719390598, 6524090962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
