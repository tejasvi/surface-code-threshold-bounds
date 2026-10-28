import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5804 = true := by
  decide +kernel

theorem tot5804 : totK PD2M8K2 D2M8K2.t5804 = [0, 182226624387, 473083503778, 249839111825, 23099921452, 0, 0, 0] := by
  decide +kernel

theorem rows5805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5805 = true := by
  decide +kernel

theorem tot5805 : totK PD2M8K2 D2M8K2.t5805 = [0, 172383748415, 465147690780, 242894678229, 13419830806, 0, 0, 0] := by
  decide +kernel

theorem rows5806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5806 = true := by
  decide +kernel

theorem tot5806 : totK PD2M8K2 D2M8K2.t5806 = [0, 0, 291551873583, 500760339956, 107580631172, 2909416399, 0, 0] := by
  decide +kernel

theorem rows5807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5807 = true := by
  decide +kernel

theorem tot5807 : totK PD2M8K2 D2M8K2.t5807 = [0, 70597915048, 315708362641, 391656423533, 98739352998, 2250452236, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
