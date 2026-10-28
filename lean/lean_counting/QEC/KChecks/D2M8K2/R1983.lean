import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7932 = true := by
  decide +kernel

theorem tot7932 : totK PD2M8K2 D2M8K2.t7932 = [0, 0, 93184785870, 426537079931, 335024496339, 28001628463, 0, 0] := by
  decide +kernel

theorem rows7933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7933 = true := by
  decide +kernel

theorem tot7933 : totK PD2M8K2 D2M8K2.t7933 = [0, 0, 171826152333, 437349012978, 255564218641, 28933192474, 0, 0] := by
  decide +kernel

theorem rows7934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7934 = true := by
  decide +kernel

theorem tot7934 : totK PD2M8K2 D2M8K2.t7934 = [0, 0, 175131359447, 481196983575, 237773552321, 11444198350, 0, 0] := by
  decide +kernel

theorem rows7935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7935 = true := by
  decide +kernel

theorem tot7935 : totK PD2M8K2 D2M8K2.t7935 = [0, 0, 190059372449, 484747347199, 214191986049, 11051716772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
