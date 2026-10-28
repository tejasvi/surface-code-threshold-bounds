import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3936 = true := by
  decide +kernel

theorem tot3936 : totK PD2M8K2 D2M8K2.t3936 = [0, 0, 204818974569, 486348841811, 219052096163, 13131754800, 0, 0] := by
  decide +kernel

theorem rows3937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3937 = true := by
  decide +kernel

theorem tot3937 : totK PD2M8K2 D2M8K2.t3937 = [0, 0, 268323564150, 478935002038, 146553060866, 7643035711, 0, 0] := by
  decide +kernel

theorem rows3938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3938 = true := by
  decide +kernel

theorem tot3938 : totK PD2M8K2 D2M8K2.t3938 = [0, 0, 179359223802, 479757807963, 231145267979, 12393374569, 0, 0] := by
  decide +kernel

theorem rows3939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3939 = true := by
  decide +kernel

theorem tot3939 : totK PD2M8K2 D2M8K2.t3939 = [0, 0, 166919215541, 456172243543, 231928784702, 14822918794, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
