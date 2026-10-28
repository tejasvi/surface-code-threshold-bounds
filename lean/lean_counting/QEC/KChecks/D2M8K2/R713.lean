import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2852 = true := by
  decide +kernel

theorem tot2852 : totK PD2M8K2 D2M8K2.t2852 = [0, 0, 219035494737, 497772669114, 166962550328, 5218872685, 0, 0] := by
  decide +kernel

theorem rows2853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2853 = true := by
  decide +kernel

theorem tot2853 : totK PD2M8K2 D2M8K2.t2853 = [0, 185018637098, 434276330028, 251955655595, 29785417251, 0, 0, 0] := by
  decide +kernel

theorem rows2854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2854 = true := by
  decide +kernel

theorem tot2854 : totK PD2M8K2 D2M8K2.t2854 = [0, 188751032004, 459324835542, 237210611130, 16795527843, 0, 0, 0] := by
  decide +kernel

theorem rows2855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2855 = true := by
  decide +kernel

theorem tot2855 : totK PD2M8K2 D2M8K2.t2855 = [0, 37079896223, 382810811913, 432471381097, 46725509957, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
