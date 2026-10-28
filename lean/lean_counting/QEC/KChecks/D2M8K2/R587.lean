import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2348 = true := by
  decide +kernel

theorem tot2348 : totK PD2M8K2 D2M8K2.t2348 = [0, 152199982118, 455021015907, 287202837179, 23500987019, 0, 0, 0] := by
  decide +kernel

theorem rows2349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2349 = true := by
  decide +kernel

theorem tot2349 : totK PD2M8K2 D2M8K2.t2349 = [0, 0, 223588225717, 488411140346, 165707350699, 4967996017, 0, 0] := by
  decide +kernel

theorem rows2350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2350 = true := by
  decide +kernel

theorem tot2350 : totK PD2M8K2 D2M8K2.t2350 = [0, 0, 182802396363, 456281560501, 227819894154, 17074942803, 0, 0] := by
  decide +kernel

theorem rows2351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2351 = true := by
  decide +kernel

theorem tot2351 : totK PD2M8K2 D2M8K2.t2351 = [0, 0, 194765737647, 487727285263, 201252230279, 9840992866, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
