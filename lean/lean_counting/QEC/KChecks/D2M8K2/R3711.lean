import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14844 = true := by
  decide +kernel

theorem tot14844 : totK PD2M8K2 D2M8K2.t14844 = [0, 187382329332, 465979806366, 239816771159, 13350822137, 0, 0, 0] := by
  decide +kernel

theorem rows14845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14845 = true := by
  decide +kernel

theorem tot14845 : totK PD2M8K2 D2M8K2.t14845 = [71330800359, 241000177194, 389887237474, 182119621462, 8209296672, 0, 0, 0] := by
  decide +kernel

theorem rows14846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14846 = true := by
  decide +kernel

theorem tot14846 : totK PD2M8K2 D2M8K2.t14846 = [189117047962, 466492656843, 253047956019, 23042648846, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14847 = true := by
  decide +kernel

theorem tot14847 : totK PD2M8K2 D2M8K2.t14847 = [179569943838, 479751514678, 231201992881, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
