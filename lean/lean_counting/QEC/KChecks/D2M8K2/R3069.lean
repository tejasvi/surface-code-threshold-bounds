import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12276 = true := by
  decide +kernel

theorem tot12276 : totK PD2M8K2 D2M8K2.t12276 = [176432921963, 460031583543, 239240099010, 17111997474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12277 = true := by
  decide +kernel

theorem tot12277 : totK PD2M8K2 D2M8K2.t12277 = [140211066889, 430704999570, 282628264713, 23472053450, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12278 = true := by
  decide +kernel

theorem tot12278 : totK PD2M8K2 D2M8K2.t12278 = [0, 272723773092, 503455826325, 112068969313, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows12279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12279 = true := by
  decide +kernel

theorem tot12279 : totK PD2M8K2 D2M8K2.t12279 = [147788873918, 407727249375, 326223555723, 41718553900, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
