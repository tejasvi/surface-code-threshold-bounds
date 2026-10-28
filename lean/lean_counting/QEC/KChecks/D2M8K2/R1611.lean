import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6444 = true := by
  decide +kernel

theorem tot6444 : totK PD2M8K2 D2M8K2.t6444 = [165316035488, 461909810789, 251101201753, 13632511348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6445 = true := by
  decide +kernel

theorem tot6445 : totK PD2M8K2 D2M8K2.t6445 = [0, 277528342906, 506960316855, 111178863578, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6446 = true := by
  decide +kernel

theorem tot6446 : totK PD2M8K2 D2M8K2.t6446 = [22230877294, 202336817421, 448864062878, 188629392179, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows6447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6447 = true := by
  decide +kernel

theorem tot6447 : totK PD2M8K2 D2M8K2.t6447 = [207330615482, 473066221409, 207862754287, 15887505222, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
