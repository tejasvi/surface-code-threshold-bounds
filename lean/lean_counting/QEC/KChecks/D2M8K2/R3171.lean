import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12684 = true := by
  decide +kernel

theorem tot12684 : totK PD2M8K2 D2M8K2.t12684 = [0, 0, 83550429232, 333416359221, 366586621937, 94805207365, 3821179711, 0] := by
  decide +kernel

theorem rows12685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12685 = true := by
  decide +kernel

theorem tot12685 : totK PD2M8K2 D2M8K2.t12685 = [0, 0, 207824138965, 464670002173, 231324448633, 15756327770, 0, 0] := by
  decide +kernel

theorem rows12686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12686 = true := by
  decide +kernel

theorem tot12686 : totK PD2M8K2 D2M8K2.t12686 = [0, 0, 202021132887, 486419618640, 210319161029, 10553281754, 0, 0] := by
  decide +kernel

theorem rows12687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12687 = true := by
  decide +kernel

theorem tot12687 : totK PD2M8K2 D2M8K2.t12687 = [0, 0, 177951497202, 439691846313, 233812893018, 17115888737, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
