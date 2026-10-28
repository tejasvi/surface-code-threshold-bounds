import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7996 = true := by
  decide +kernel

theorem tot7996 : totK PD2M8K2 D2M8K2.t7996 = [0, 0, 0, 198372397453, 479562047429, 186738942845, 11885407614, 0] := by
  decide +kernel

theorem rows7997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7997 = true := by
  decide +kernel

theorem tot7997 : totK PD2M8K2 D2M8K2.t7997 = [0, 0, 169727365698, 445755346390, 258314880054, 21505951547, 0, 0] := by
  decide +kernel

theorem rows7998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7998 = true := by
  decide +kernel

theorem tot7998 : totK PD2M8K2 D2M8K2.t7998 = [0, 0, 193892168579, 451931435270, 223551451199, 15985401012, 0, 0] := by
  decide +kernel

theorem rows7999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7999 = true := by
  decide +kernel

theorem tot7999 : totK PD2M8K2 D2M8K2.t7999 = [0, 0, 55085801213, 339511465321, 410892430909, 72223889780, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
