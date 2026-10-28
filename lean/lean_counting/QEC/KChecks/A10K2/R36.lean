import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t144 = true := by
  decide +kernel

theorem tot144 : totK PA10K2 A10K2.t144 = [0, 479359807812, 1850896986218, 1895366590941, 490379749166, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t145 = true := by
  decide +kernel

theorem tot145 : totK PA10K2 A10K2.t145 = [554944724842, 1820757913840, 1774299331536, 627916308492, 64552209838, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t146 = true := by
  decide +kernel

theorem tot146 : totK PA10K2 A10K2.t146 = [0, 813785329316, 2268269522065, 1407649069868, 176549393250, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t147 = true := by
  decide +kernel

theorem tot147 : totK PA10K2 A10K2.t147 = [495062425814, 1819531637352, 1948291059484, 622567682289, 106566586512, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
