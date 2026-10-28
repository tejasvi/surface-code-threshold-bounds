import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8168 = true := by
  decide +kernel

theorem tot8168 : totK PD2M8K2 D2M8K2.t8168 = [0, 0, 153126639262, 461246542818, 251512316280, 15633226429, 0, 0] := by
  decide +kernel

theorem rows8169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8169 = true := by
  decide +kernel

theorem tot8169 : totK PD2M8K2 D2M8K2.t8169 = [0, 0, 0, 292538310395, 488277451611, 72140644884, 1239866073, 0] := by
  decide +kernel

theorem rows8170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8170 = true := by
  decide +kernel

theorem tot8170 : totK PD2M8K2 D2M8K2.t8170 = [0, 0, 162149715619, 439687461097, 291301675541, 32693043629, 0, 0] := by
  decide +kernel

theorem rows8171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8171 = true := by
  decide +kernel

theorem tot8171 : totK PD2M8K2 D2M8K2.t8171 = [0, 0, 190579348167, 487962639436, 229733246272, 9787993597, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
