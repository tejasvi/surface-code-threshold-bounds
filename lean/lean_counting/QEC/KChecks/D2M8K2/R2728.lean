import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10912 = true := by
  decide +kernel

theorem tot10912 : totK PD2M8K2 D2M8K2.t10912 = [0, 125598274321, 422123008020, 325749456347, 31877896553, 0, 0, 0] := by
  decide +kernel

theorem rows10913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10913 = true := by
  decide +kernel

theorem tot10913 : totK PD2M8K2 D2M8K2.t10913 = [0, 0, 209724576040, 483525875862, 173450424993, 7832068735, 0, 0] := by
  decide +kernel

theorem rows10914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10914 = true := by
  decide +kernel

theorem tot10914 : totK PD2M8K2 D2M8K2.t10914 = [0, 138064893235, 389938715526, 311410953678, 60252144735, 980350181, 0, 0] := by
  decide +kernel

theorem rows10915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10915 = true := by
  decide +kernel

theorem tot10915 : totK PD2M8K2 D2M8K2.t10915 = [0, 161498793696, 441651670631, 280292508434, 30271926621, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
