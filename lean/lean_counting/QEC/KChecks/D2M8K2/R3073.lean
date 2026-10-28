import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12292 = true := by
  decide +kernel

theorem tot12292 : totK PD2M8K2 D2M8K2.t12292 = [164686214008, 408569249181, 265979153351, 61221898786, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows12293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12293 = true := by
  decide +kernel

theorem tot12293 : totK PD2M8K2 D2M8K2.t12293 = [161587966196, 444805043888, 281685420020, 25230138071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12294 = true := by
  decide +kernel

theorem tot12294 : totK PD2M8K2 D2M8K2.t12294 = [0, 233725516815, 494764594322, 151957530752, 2333843204, 0, 0, 0] := by
  decide +kernel

theorem rows12295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12295 = true := by
  decide +kernel

theorem tot12295 : totK PD2M8K2 D2M8K2.t12295 = [0, 186600508105, 470896167067, 211324295699, 14799667681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
