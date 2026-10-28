import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t748 = true := by
  decide +kernel

theorem tot748 : totK PD2M8K2 D2M8K2.t748 = [0, 157620364114, 453898632652, 273342604315, 25489256278, 0, 0, 0] := by
  decide +kernel

theorem rows749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t749 = true := by
  decide +kernel

theorem tot749 : totK PD2M8K2 D2M8K2.t749 = [0, 88734127824, 357321855985, 376845280741, 67033531678, 1075657031, 0, 0] := by
  decide +kernel

theorem rows750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t750 = true := by
  decide +kernel

theorem tot750 : totK PD2M8K2 D2M8K2.t750 = [0, 53923645477, 299814581363, 425838391569, 109206953762, 3804183361, 0, 0] := by
  decide +kernel

theorem rows751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t751 = true := by
  decide +kernel

theorem tot751 : totK PD2M8K2 D2M8K2.t751 = [0, 183886098471, 455563054437, 242089741519, 20736899787, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
