import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10972 = true := by
  decide +kernel

theorem tot10972 : totK PD2M8K2 D2M8K2.t10972 = [0, 170216491020, 469908750309, 228542036119, 9495229574, 0, 0, 0] := by
  decide +kernel

theorem rows10973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10973 = true := by
  decide +kernel

theorem tot10973 : totK PD2M8K2 D2M8K2.t10973 = [0, 176175403182, 463580262824, 234973042943, 11616684087, 0, 0, 0] := by
  decide +kernel

theorem rows10974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10974 = true := by
  decide +kernel

theorem tot10974 : totK PD2M8K2 D2M8K2.t10974 = [179595312347, 456748385007, 219448943003, 43581976419, 8621106361, 0, 0, 0] := by
  decide +kernel

theorem rows10975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10975 = true := by
  decide +kernel

theorem tot10975 : totK PD2M8K2 D2M8K2.t10975 = [204531510822, 458427513251, 204943048784, 12530154330, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
