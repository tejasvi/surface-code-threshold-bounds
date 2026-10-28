import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16132 = true := by
  decide +kernel

theorem tot16132 : totK PD2M8K2 D2M8K2.t16132 = [0, 182119805919, 423426897897, 291214542505, 39299215645, 0, 0, 0] := by
  decide +kernel

theorem rows16133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16133 = true := by
  decide +kernel

theorem tot16133 : totK PD2M8K2 D2M8K2.t16133 = [0, 148031037364, 477064157205, 262575345326, 15244020503, 0, 0, 0] := by
  decide +kernel

theorem rows16134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16134 = true := by
  decide +kernel

theorem tot16134 : totK PD2M8K2 D2M8K2.t16134 = [0, 88453318852, 320705574272, 361919098225, 130727985004, 15615182729, 0, 0] := by
  decide +kernel

theorem rows16135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16135 = true := by
  decide +kernel

theorem tot16135 : totK PD2M8K2 D2M8K2.t16135 = [0, 0, 187331943289, 465907372985, 241852722236, 12129075023, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
