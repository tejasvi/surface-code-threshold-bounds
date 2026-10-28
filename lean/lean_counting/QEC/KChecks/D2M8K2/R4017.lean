import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16068 = true := by
  decide +kernel

theorem tot16068 : totK PD2M8K2 D2M8K2.t16068 = [0, 0, 265054498687, 512328767600, 123000018529, 1198073392, 0, 0] := by
  decide +kernel

theorem rows16069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16069 = true := by
  decide +kernel

theorem tot16069 : totK PD2M8K2 D2M8K2.t16069 = [0, 57940408170, 245900710682, 408507319294, 156415154844, 7718595657, 0, 0] := by
  decide +kernel

theorem rows16070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16070 = true := by
  decide +kernel

theorem tot16070 : totK PD2M8K2 D2M8K2.t16070 = [0, 191514908489, 487726758805, 202600948981, 6795265341, 0, 0, 0] := by
  decide +kernel

theorem rows16071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16071 = true := by
  decide +kernel

theorem tot16071 : totK PD2M8K2 D2M8K2.t16071 = [0, 71179355405, 361928577145, 378453959111, 63661352268, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
