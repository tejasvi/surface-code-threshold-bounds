import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11780 = true := by
  decide +kernel

theorem tot11780 : totK PD2M8K2 D2M8K2.t11780 = [0, 184918025719, 470687712173, 217240248355, 12154716328, 0, 0, 0] := by
  decide +kernel

theorem rows11781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11781 = true := by
  decide +kernel

theorem tot11781 : totK PD2M8K2 D2M8K2.t11781 = [0, 136485500649, 435077147237, 283332344048, 21564707405, 0, 0, 0] := by
  decide +kernel

theorem rows11782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11782 = true := by
  decide +kernel

theorem tot11782 : totK PD2M8K2 D2M8K2.t11782 = [0, 0, 278179706651, 498137669869, 96114076967, 1334361349, 0, 0] := by
  decide +kernel

theorem rows11783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11783 = true := by
  decide +kernel

theorem tot11783 : totK PD2M8K2 D2M8K2.t11783 = [0, 146499304292, 404377811028, 337929804071, 39947287535, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
