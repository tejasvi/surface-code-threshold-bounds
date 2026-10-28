import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13204 = true := by
  decide +kernel

theorem tot13204 : totK PD2M8K2 D2M8K2.t13204 = [0, 0, 182039932910, 459456171181, 228117019672, 17385499678, 0, 0] := by
  decide +kernel

theorem rows13205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13205 = true := by
  decide +kernel

theorem tot13205 : totK PD2M8K2 D2M8K2.t13205 = [0, 0, 207260688219, 487482128773, 183357183298, 5169667809, 0, 0] := by
  decide +kernel

theorem rows13206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13206 = true := by
  decide +kernel

theorem tot13206 : totK PD2M8K2 D2M8K2.t13206 = [0, 0, 98501146869, 397646936369, 329578157943, 46544892551, 1310285577, 0] := by
  decide +kernel

theorem rows13207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13207 = true := by
  decide +kernel

theorem tot13207 : totK PD2M8K2 D2M8K2.t13207 = [0, 0, 37755103912, 348555574295, 452362935512, 44603406665, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
