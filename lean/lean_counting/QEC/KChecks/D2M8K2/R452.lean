import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1808 = true := by
  decide +kernel

theorem tot1808 : totK PD2M8K2 D2M8K2.t1808 = [0, 93978096042, 298199644128, 358559493107, 163996436971, 13468148062, 0, 0] := by
  decide +kernel

theorem rows1809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1809 = true := by
  decide +kernel

theorem tot1809 : totK PD2M8K2 D2M8K2.t1809 = [0, 162362327520, 446293828692, 279534815281, 23743150253, 0, 0, 0] := by
  decide +kernel

theorem rows1810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1810 = true := by
  decide +kernel

theorem tot1810 : totK PD2M8K2 D2M8K2.t1810 = [0, 174066083134, 465971418068, 246909996827, 16691637124, 0, 0, 0] := by
  decide +kernel

theorem rows1811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1811 = true := by
  decide +kernel

theorem tot1811 : totK PD2M8K2 D2M8K2.t1811 = [0, 0, 170569310490, 451551757933, 263175873751, 25373788367, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
