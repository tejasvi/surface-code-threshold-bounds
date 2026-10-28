import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t560 = true := by
  decide +kernel

theorem tot560 : totK PD2M8K2 D2M8K2.t560 = [0, 0, 214643304010, 498063623947, 174236455860, 2991720150, 0, 0] := by
  decide +kernel

theorem rows561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t561 = true := by
  decide +kernel

theorem tot561 : totK PD2M8K2 D2M8K2.t561 = [0, 0, 185463846596, 458902118397, 228251258595, 18095854657, 0, 0] := by
  decide +kernel

theorem rows562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t562 = true := by
  decide +kernel

theorem tot562 : totK PD2M8K2 D2M8K2.t562 = [0, 0, 206180450543, 475209695941, 183976724929, 7651299259, 0, 0] := by
  decide +kernel

theorem rows563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t563 = true := by
  decide +kernel

theorem tot563 : totK PD2M8K2 D2M8K2.t563 = [0, 0, 240924752014, 500402302601, 136297319802, 2263942262, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
