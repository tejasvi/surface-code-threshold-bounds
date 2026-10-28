import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13820 = true := by
  decide +kernel

theorem tot13820 : totK PD2M8K2 D2M8K2.t13820 = [134864601914, 398753066247, 357140309905, 47124937013, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13821 = true := by
  decide +kernel

theorem tot13821 : totK PD2M8K2 D2M8K2.t13821 = [194448797752, 468419619779, 224504108987, 15135916913, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13822 = true := by
  decide +kernel

theorem tot13822 : totK PD2M8K2 D2M8K2.t13822 = [95841475714, 428523563559, 345167449631, 38642930997, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13823 = true := by
  decide +kernel

theorem tot13823 : totK PD2M8K2 D2M8K2.t13823 = [0, 161716995139, 453228852121, 270332983565, 25368447013, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
