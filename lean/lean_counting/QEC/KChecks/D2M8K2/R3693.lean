import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14772 = true := by
  decide +kernel

theorem tot14772 : totK PD2M8K2 D2M8K2.t14772 = [169516199784, 466151343369, 252225402469, 15497453971, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14773 = true := by
  decide +kernel

theorem tot14773 : totK PD2M8K2 D2M8K2.t14773 = [87922896509, 343861133039, 385408267809, 85588973811, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows14774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14774 = true := by
  decide +kernel

theorem tot14774 : totK PD2M8K2 D2M8K2.t14774 = [0, 208299889122, 489440351706, 173045083108, 9455263945, 0, 0, 0] := by
  decide +kernel

theorem rows14775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14775 = true := by
  decide +kernel

theorem tot14775 : totK PD2M8K2 D2M8K2.t14775 = [140780261206, 393934313152, 329128126960, 65235313605, 2426619133, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
