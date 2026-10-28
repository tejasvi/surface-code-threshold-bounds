import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14856 = true := by
  decide +kernel

theorem tot14856 : totK PD2M8K2 D2M8K2.t14856 = [0, 229543414630, 495956198531, 168301578728, 4761634222, 0, 0, 0] := by
  decide +kernel

theorem rows14857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14857 = true := by
  decide +kernel

theorem tot14857 : totK PD2M8K2 D2M8K2.t14857 = [0, 182163085273, 460897975518, 226132731630, 17381584168, 0, 0, 0] := by
  decide +kernel

theorem rows14858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14858 = true := by
  decide +kernel

theorem tot14858 : totK PD2M8K2 D2M8K2.t14858 = [0, 194783422945, 475333509133, 205452127211, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows14859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14859 = true := by
  decide +kernel

theorem tot14859 : totK PD2M8K2 D2M8K2.t14859 = [0, 121665124856, 428189819007, 298564892258, 22693907379, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
