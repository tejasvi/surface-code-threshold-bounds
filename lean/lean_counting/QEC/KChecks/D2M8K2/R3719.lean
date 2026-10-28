import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14876 = true := by
  decide +kernel

theorem tot14876 : totK PD2M8K2 D2M8K2.t14876 = [93348984190, 385590761376, 389887105957, 55607401181, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14877 = true := by
  decide +kernel

theorem tot14877 : totK PD2M8K2 D2M8K2.t14877 = [174534711971, 441298382406, 268513851465, 20902932824, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14878 = true := by
  decide +kernel

theorem tot14878 : totK PD2M8K2 D2M8K2.t14878 = [159209688015, 472108749731, 270174392170, 16157238080, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14879 = true := by
  decide +kernel

theorem tot14879 : totK PD2M8K2 D2M8K2.t14879 = [0, 180073013610, 446657312119, 253013893736, 24234642673, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
