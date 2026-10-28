import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10852 = true := by
  decide +kernel

theorem tot10852 : totK PD2M8K2 D2M8K2.t10852 = [0, 130424248025, 439506242665, 317805090410, 26404042577, 0, 0, 0] := by
  decide +kernel

theorem rows10853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10853 = true := by
  decide +kernel

theorem tot10853 : totK PD2M8K2 D2M8K2.t10853 = [0, 0, 211440501746, 491530762234, 175886764305, 4967996017, 0, 0] := by
  decide +kernel

theorem rows10854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10854 = true := by
  decide +kernel

theorem tot10854 : totK PD2M8K2 D2M8K2.t10854 = [0, 0, 194868426889, 460816611515, 218517813890, 17074942803, 0, 0] := by
  decide +kernel

theorem rows10855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10855 = true := by
  decide +kernel

theorem tot10855 : totK PD2M8K2 D2M8K2.t10855 = [0, 0, 195604453635, 495442941129, 188172684138, 5616011243, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
