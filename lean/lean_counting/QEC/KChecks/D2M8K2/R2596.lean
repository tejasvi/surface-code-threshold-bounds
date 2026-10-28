import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10384 = true := by
  decide +kernel

theorem tot10384 : totK PD2M8K2 D2M8K2.t10384 = [0, 0, 160427418495, 386577372718, 280452447106, 73655258847, 3821179711, 0] := by
  decide +kernel

theorem rows10385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10385 = true := by
  decide +kernel

theorem tot10385 : totK PD2M8K2 D2M8K2.t10385 = [0, 0, 209882743056, 484016143233, 198263892039, 9698344928, 0, 0] := by
  decide +kernel

theorem rows10386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10386 = true := by
  decide +kernel

theorem tot10386 : totK PD2M8K2 D2M8K2.t10386 = [0, 0, 38115386132, 332381653606, 440827484870, 87140840181, 1268739303, 0] := by
  decide +kernel

theorem rows10387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10387 = true := by
  decide +kernel

theorem tot10387 : totK PD2M8K2 D2M8K2.t10387 = [0, 0, 0, 235358403579, 488003890637, 152104490309, 4918255160, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
