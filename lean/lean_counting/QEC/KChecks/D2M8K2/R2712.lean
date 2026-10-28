import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10848 = true := by
  decide +kernel

theorem tot10848 : totK PD2M8K2 D2M8K2.t10848 = [0, 126136851789, 436341534963, 313835330355, 25997640290, 0, 0, 0] := by
  decide +kernel

theorem rows10849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10849 = true := by
  decide +kernel

theorem tot10849 : totK PD2M8K2 D2M8K2.t10849 = [0, 0, 213747710276, 487996882757, 181528337599, 9587713104, 0, 0] := by
  decide +kernel

theorem rows10850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10850 = true := by
  decide +kernel

theorem tot10850 : totK PD2M8K2 D2M8K2.t10850 = [0, 124817758654, 419449915881, 328834298064, 39209636981, 0, 0, 0] := by
  decide +kernel

theorem rows10851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10851 = true := by
  decide +kernel

theorem tot10851 : totK PD2M8K2 D2M8K2.t10851 = [0, 171885659356, 446116530907, 273011342033, 28316863052, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
