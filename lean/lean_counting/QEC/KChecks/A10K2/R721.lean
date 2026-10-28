import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2884 = true := by
  decide +kernel

theorem tot2884 : totK PA10K2 A10K2.t2884 = [0, 492752704009, 1803896404914, 1979623244356, 597558976490, 37431387394, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2885 = true := by
  decide +kernel

theorem tot2885 : totK PA10K2 A10K2.t2885 = [0, 122360162702, 986817744892, 2126254014409, 1470412550473, 247012151628, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows2886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2886 = true := by
  decide +kernel

theorem tot2886 : totK PA10K2 A10K2.t2886 = [0, 0, 542473515650, 2013314050770, 2019548728678, 474994761051, 12813073358, 0, 0, 0] := by
  decide +kernel

theorem rows2887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2887 = true := by
  decide +kernel

theorem tot2887 : totK PA10K2 A10K2.t2887 = [480657707117, 1575325675077, 1472779444749, 506547077169, 411677375099, 301047167938, 43287591117, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
