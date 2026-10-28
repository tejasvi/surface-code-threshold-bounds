import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1904 = true := by
  decide +kernel

theorem tot1904 : totK PD2M8K2 D2M8K2.t1904 = [0, 0, 164321677495, 470401872370, 241370157430, 13673275291, 0, 0] := by
  decide +kernel

theorem rows1905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1905 = true := by
  decide +kernel

theorem tot1905 : totK PD2M8K2 D2M8K2.t1905 = [0, 0, 0, 310867446709, 450372556454, 86524432709, 1095107716, 0] := by
  decide +kernel

theorem rows1906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1906 = true := by
  decide +kernel

theorem tot1906 : totK PD2M8K2 D2M8K2.t1906 = [0, 141810093519, 295373991377, 165630481171, 202641378413, 81166966017, 3882006667, 0] := by
  decide +kernel

theorem rows1907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1907 = true := by
  decide +kernel

theorem tot1907 : totK PD2M8K2 D2M8K2.t1907 = [0, 180106242723, 457428338766, 228293675370, 17075881721, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
