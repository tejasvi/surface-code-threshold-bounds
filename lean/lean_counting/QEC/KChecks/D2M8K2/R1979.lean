import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7916 = true := by
  decide +kernel

theorem tot7916 : totK PD2M8K2 D2M8K2.t7916 = [0, 0, 172502767250, 488372148186, 227413004266, 6616174017, 0, 0] := by
  decide +kernel

theorem rows7917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7917 = true := by
  decide +kernel

theorem tot7917 : totK PD2M8K2 D2M8K2.t7917 = [0, 172708002957, 432677447952, 242226060197, 53861090818, 4226847275, 0, 0] := by
  decide +kernel

theorem rows7918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7918 = true := by
  decide +kernel

theorem tot7918 : totK PD2M8K2 D2M8K2.t7918 = [0, 180689127508, 466672807475, 242679360166, 14817511569, 0, 0, 0] := by
  decide +kernel

theorem rows7919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7919 = true := by
  decide +kernel

theorem tot7919 : totK PD2M8K2 D2M8K2.t7919 = [0, 68338813936, 329857282753, 405336550049, 87217092657, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
