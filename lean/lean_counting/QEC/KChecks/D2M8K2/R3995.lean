import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15980 = true := by
  decide +kernel

theorem tot15980 : totK PD2M8K2 D2M8K2.t15980 = [0, 0, 159084807754, 351906397204, 299060969778, 116808238749, 8863302705, 0] := by
  decide +kernel

theorem rows15981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15981 = true := by
  decide +kernel

theorem tot15981 : totK PD2M8K2 D2M8K2.t15981 = [0, 0, 191732990540, 475845563069, 229265055839, 12670579584, 0, 0] := by
  decide +kernel

theorem rows15982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15982 = true := by
  decide +kernel

theorem tot15982 : totK PD2M8K2 D2M8K2.t15982 = [0, 0, 89061927447, 394489235364, 370274068826, 66174979843, 2964756734, 0] := by
  decide +kernel

theorem rows15983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15983 = true := by
  decide +kernel

theorem tot15983 : totK PD2M8K2 D2M8K2.t15983 = [0, 0, 0, 253159877143, 469535090591, 190907497242, 7622332832, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
