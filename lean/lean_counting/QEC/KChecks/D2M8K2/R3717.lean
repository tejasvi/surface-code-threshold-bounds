import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14868 = true := by
  decide +kernel

theorem tot14868 : totK PD2M8K2 D2M8K2.t14868 = [0, 188594108023, 461101510018, 252273072055, 18418208341, 0, 0, 0] := by
  decide +kernel

theorem rows14869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14869 = true := by
  decide +kernel

theorem tot14869 : totK PD2M8K2 D2M8K2.t14869 = [0, 55408972850, 352659801050, 392182242437, 62014751882, 1053411165, 0, 0] := by
  decide +kernel

theorem rows14870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14870 = true := by
  decide +kernel

theorem tot14870 : totK PD2M8K2 D2M8K2.t14870 = [0, 89029495941, 345438230688, 343253570223, 84904045944, 3667207281, 0, 0] := by
  decide +kernel

theorem rows14871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14871 = true := by
  decide +kernel

theorem tot14871 : totK PD2M8K2 D2M8K2.t14871 = [0, 188557332365, 447582946982, 250503524736, 23373855263, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
