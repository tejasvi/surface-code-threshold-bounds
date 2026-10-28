import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12048 = true := by
  decide +kernel

theorem tot12048 : totK PD2M8K2 D2M8K2.t12048 = [0, 0, 283578263992, 515180935576, 90539374013, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12049 = true := by
  decide +kernel

theorem tot12049 : totK PD2M8K2 D2M8K2.t12049 = [0, 90796588535, 340460834806, 357887440838, 92286237965, 3821179711, 0, 0] := by
  decide +kernel

theorem rows12050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12050 = true := by
  decide +kernel

theorem tot12050 : totK PD2M8K2 D2M8K2.t12050 = [0, 201968488757, 456931466160, 219562618305, 20964581341, 0, 0, 0] := by
  decide +kernel

theorem rows12051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12051 = true := by
  decide +kernel

theorem tot12051 : totK PD2M8K2 D2M8K2.t12051 = [0, 89984030014, 385742199377, 368062613296, 49818139276, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
