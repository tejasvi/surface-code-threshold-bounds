import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4932 = true := by
  decide +kernel

theorem tot4932 : totK PD2M8K2 D2M8K2.t4932 = [0, 0, 171030954193, 456515571234, 264965761718, 19118645393, 0, 0] := by
  decide +kernel

theorem rows4933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4933 = true := by
  decide +kernel

theorem tot4933 : totK PD2M8K2 D2M8K2.t4933 = [0, 0, 90054624902, 344932535179, 377660759656, 88691310119, 1268739303, 0] := by
  decide +kernel

theorem rows4934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4934 = true := by
  decide +kernel

theorem tot4934 : totK PD2M8K2 D2M8K2.t4934 = [0, 0, 0, 236146527517, 493560467274, 154607924132, 5106924707, 0] := by
  decide +kernel

theorem rows4935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4935 = true := by
  decide +kernel

theorem tot4935 : totK PD2M8K2 D2M8K2.t4935 = [0, 91454885225, 217174660516, 169788965304, 265178781845, 144203103588, 11902596887, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
