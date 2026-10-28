import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14984 = true := by
  decide +kernel

theorem tot14984 : totK PD2M8K2 D2M8K2.t14984 = [0, 0, 207091905010, 475180467636, 160738197434, 5163947488, 0, 0] := by
  decide +kernel

theorem rows14985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14985 = true := by
  decide +kernel

theorem tot14985 : totK PD2M8K2 D2M8K2.t14985 = [0, 0, 19330912284, 313264961615, 442997533814, 69155860623, 1166720416, 0] := by
  decide +kernel

theorem rows14986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14986 = true := by
  decide +kernel

theorem tot14986 : totK PD2M8K2 D2M8K2.t14986 = [0, 0, 105939967494, 438959855444, 325126459892, 22999951857, 0, 0] := by
  decide +kernel

theorem rows14987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14987 = true := by
  decide +kernel

theorem tot14987 : totK PD2M8K2 D2M8K2.t14987 = [0, 0, 288986835487, 486848297834, 139892087387, 2939453538, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
