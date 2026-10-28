import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5880 = true := by
  decide +kernel

theorem tot5880 : totK PD2M8K2 D2M8K2.t5880 = [0, 54664046510, 376671291828, 378823299864, 59670095265, 1053411165, 0, 0] := by
  decide +kernel

theorem rows5881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5881 = true := by
  decide +kernel

theorem tot5881 : totK PD2M8K2 D2M8K2.t5881 = [0, 67973715857, 297479983334, 391175669762, 96940037781, 3667207281, 0, 0] := by
  decide +kernel

theorem rows5882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5882 = true := by
  decide +kernel

theorem tot5882 : totK PD2M8K2 D2M8K2.t5882 = [0, 157526551100, 458461730980, 272611990730, 21973649153, 0, 0, 0] := by
  decide +kernel

theorem rows5883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5883 = true := by
  decide +kernel

theorem tot5883 : totK PD2M8K2 D2M8K2.t5883 = [0, 179279935282, 458354706635, 250830642611, 16035124244, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
