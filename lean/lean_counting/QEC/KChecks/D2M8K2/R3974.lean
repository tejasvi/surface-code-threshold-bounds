import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15896 = true := by
  decide +kernel

theorem tot15896 : totK PD2M8K2 D2M8K2.t15896 = [0, 165522226222, 439104310484, 282697917287, 30020043788, 0, 0, 0] := by
  decide +kernel

theorem rows15897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15897 = true := by
  decide +kernel

theorem tot15897 : totK PD2M8K2 D2M8K2.t15897 = [0, 91483120367, 396586196772, 347000072366, 52267619092, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15898 = true := by
  decide +kernel

theorem tot15898 : totK PD2M8K2 D2M8K2.t15898 = [0, 0, 228413929366, 493848880569, 166159436848, 8470662040, 0, 0] := by
  decide +kernel

theorem rows15899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15899 = true := by
  decide +kernel

theorem tot15899 : totK PD2M8K2 D2M8K2.t15899 = [0, 103750404885, 346308893969, 337224801021, 91655162277, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
