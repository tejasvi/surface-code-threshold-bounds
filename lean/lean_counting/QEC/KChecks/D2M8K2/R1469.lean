import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5876 = true := by
  decide +kernel

theorem tot5876 : totK PD2M8K2 D2M8K2.t5876 = [0, 83317562688, 353391222635, 372003277276, 78940178956, 1171084559, 0, 0] := by
  decide +kernel

theorem rows5877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5877 = true := by
  decide +kernel

theorem tot5877 : totK PD2M8K2 D2M8K2.t5877 = [0, 0, 198234342299, 464338006956, 178379539324, 10425178834, 0, 0] := by
  decide +kernel

theorem rows5878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5878 = true := by
  decide +kernel

theorem tot5878 : totK PD2M8K2 D2M8K2.t5878 = [0, 154436770903, 447541199993, 268448777989, 31201001410, 1509187004, 0, 0] := by
  decide +kernel

theorem rows5879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5879 = true := by
  decide +kernel

theorem tot5879 : totK PD2M8K2 D2M8K2.t5879 = [0, 190027189902, 462723110059, 230658563246, 13482942092, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
