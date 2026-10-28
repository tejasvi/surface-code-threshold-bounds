import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13844 = true := by
  decide +kernel

theorem tot13844 : totK PD2M8K2 D2M8K2.t13844 = [0, 130629766741, 442863811063, 288599988683, 20967958308, 0, 0, 0] := by
  decide +kernel

theorem rows13845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13845 = true := by
  decide +kernel

theorem tot13845 : totK PD2M8K2 D2M8K2.t13845 = [0, 0, 218153840372, 464986366707, 175570188873, 9579374723, 0, 0] := by
  decide +kernel

theorem rows13846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13846 = true := by
  decide +kernel

theorem tot13846 : totK PD2M8K2 D2M8K2.t13846 = [0, 83307051912, 337017395418, 347823862707, 87410627317, 3436822651, 0, 0] := by
  decide +kernel

theorem rows13847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13847 = true := by
  decide +kernel

theorem tot13847 : totK PD2M8K2 D2M8K2.t13847 = [0, 191951111820, 462211511699, 240608108115, 18252358503, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
