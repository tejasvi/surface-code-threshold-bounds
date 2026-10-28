import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2956 = true := by
  decide +kernel

theorem tot2956 : totK PA10K2 A10K2.t2956 = [0, 580780067701, 1934574594448, 1761055952437, 418976650888, 24788305136, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2957 = true := by
  decide +kernel

theorem tot2957 : totK PA10K2 A10K2.t2957 = [0, 17057514467, 809182730527, 2089714109825, 1577180991616, 332909360382, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows2958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2958 = true := by
  decide +kernel

theorem tot2958 : totK PA10K2 A10K2.t2958 = [0, 298738363490, 1319518037090, 2035620915970, 1087074865430, 132238667714, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2959 = true := by
  decide +kernel

theorem tot2959 : totK PA10K2 A10K2.t2959 = [0, 470491761713, 1844288099952, 2063148913678, 604628148373, 24171634998, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
