import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14788 = true := by
  decide +kernel

theorem tot14788 : totK PD2M8K2 D2M8K2.t14788 = [0, 158815746518, 446086554003, 281270997081, 30333897086, 0, 0, 0] := by
  decide +kernel

theorem rows14789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14789 = true := by
  decide +kernel

theorem tot14789 : totK PD2M8K2 D2M8K2.t14789 = [0, 133969283653, 443948993400, 292654831017, 18811779427, 0, 0, 0] := by
  decide +kernel

theorem rows14790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14790 = true := by
  decide +kernel

theorem tot14790 : totK PD2M8K2 D2M8K2.t14790 = [0, 0, 246046899457, 503908232272, 139194395434, 4009909289, 0, 0] := by
  decide +kernel

theorem rows14791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14791 = true := by
  decide +kernel

theorem tot14791 : totK PD2M8K2 D2M8K2.t14791 = [0, 157064894120, 418415415539, 276024461140, 53192184811, 1149959346, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
