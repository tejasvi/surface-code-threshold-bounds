import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14920 = true := by
  decide +kernel

theorem tot14920 : totK PD2M8K2 D2M8K2.t14920 = [0, 199295232215, 465422158174, 226979205225, 19618908590, 0, 0, 0] := by
  decide +kernel

theorem rows14921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14921 = true := by
  decide +kernel

theorem tot14921 : totK PD2M8K2 D2M8K2.t14921 = [0, 186193047837, 467064865921, 215043572522, 12420044233, 0, 0, 0] := by
  decide +kernel

theorem rows14922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14922 = true := by
  decide +kernel

theorem tot14922 : totK PD2M8K2 D2M8K2.t14922 = [0, 0, 288621340460, 495640584294, 107110771587, 1198073392, 0, 0] := by
  decide +kernel

theorem rows14923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14923 = true := by
  decide +kernel

theorem tot14923 : totK PD2M8K2 D2M8K2.t14923 = [0, 54330972770, 285774283689, 427282494971, 116203459867, 4030866388, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
