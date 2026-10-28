import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3024 = true := by
  decide +kernel

theorem tot3024 : totK PD2M8K2 D2M8K2.t3024 = [0, 0, 195198017306, 483080549249, 188826951957, 11885407614, 0, 0] := by
  decide +kernel

theorem rows3025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3025 = true := by
  decide +kernel

theorem tot3025 : totK PD2M8K2 D2M8K2.t3025 = [0, 169592521413, 446971640154, 254895407364, 26032521305, 0, 0, 0] := by
  decide +kernel

theorem rows3026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3026 = true := by
  decide +kernel

theorem tot3026 : totK PD2M8K2 D2M8K2.t3026 = [0, 198489768499, 459442108765, 221224642703, 16071213171, 0, 0, 0] := by
  decide +kernel

theorem rows3027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3027 = true := by
  decide +kernel

theorem tot3027 : totK PD2M8K2 D2M8K2.t3027 = [0, 43054642252, 336619023376, 423115247612, 71982187620, 1062926506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
