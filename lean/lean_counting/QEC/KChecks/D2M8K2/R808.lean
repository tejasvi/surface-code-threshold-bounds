import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3232 = true := by
  decide +kernel

theorem tot3232 : totK PD2M8K2 D2M8K2.t3232 = [0, 169808334766, 449097186271, 252015397240, 17575085233, 0, 0, 0] := by
  decide +kernel

theorem rows3233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3233 = true := by
  decide +kernel

theorem tot3233 : totK PD2M8K2 D2M8K2.t3233 = [0, 92498175148, 365998411141, 340838353138, 62430601595, 1095107716, 0, 0] := by
  decide +kernel

theorem rows3234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3234 = true := by
  decide +kernel

theorem tot3234 : totK PD2M8K2 D2M8K2.t3234 = [0, 0, 320147559432, 469181413518, 82109342826, 1067409660, 0, 0] := by
  decide +kernel

theorem rows3235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3235 = true := by
  decide +kernel

theorem tot3235 : totK PD2M8K2 D2M8K2.t3235 = [174930887950, 422386189647, 172958118462, 70866072843, 48775271745, 2814597007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
