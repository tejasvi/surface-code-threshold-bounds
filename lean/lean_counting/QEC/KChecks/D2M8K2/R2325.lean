import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9300 = true := by
  decide +kernel

theorem tot9300 : totK PD2M8K2 D2M8K2.t9300 = [32063946520, 207061452630, 431906896610, 182302062890, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows9301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9301 = true := by
  decide +kernel

theorem tot9301 : totK PD2M8K2 D2M8K2.t9301 = [180989514747, 457171127000, 250810179256, 23115844934, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9302 = true := by
  decide +kernel

theorem tot9302 : totK PD2M8K2 D2M8K2.t9302 = [189447941638, 479391022532, 226939995634, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9303 = true := by
  decide +kernel

theorem tot9303 : totK PD2M8K2 D2M8K2.t9303 = [15335530501, 303675734332, 471431751235, 99864274930, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
