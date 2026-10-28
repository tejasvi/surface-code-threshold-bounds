import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10884 = true := by
  decide +kernel

theorem tot10884 : totK PD2M8K2 D2M8K2.t10884 = [0, 92934196222, 356517979819, 376157517050, 74560376364, 1268739303, 0, 0] := by
  decide +kernel

theorem rows10885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10885 = true := by
  decide +kernel

theorem tot10885 : totK PD2M8K2 D2M8K2.t10885 = [0, 0, 248611848507, 497406612792, 150169083844, 3696530321, 0, 0] := by
  decide +kernel

theorem rows10886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10886 = true := by
  decide +kernel

theorem tot10886 : totK PD2M8K2 D2M8K2.t10886 = [0, 0, 182163085273, 458772471833, 230134224975, 18446688069, 0, 0] := by
  decide +kernel

theorem rows10887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10887 = true := by
  decide +kernel

theorem tot10887 : totK PD2M8K2 D2M8K2.t10887 = [0, 0, 170493004675, 481688396908, 215261337696, 9713690252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
