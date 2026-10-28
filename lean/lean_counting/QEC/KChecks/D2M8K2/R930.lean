import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3720 = true := by
  decide +kernel

theorem tot3720 : totK PD2M8K2 D2M8K2.t3720 = [8103823521, 260620241950, 439702077714, 194447141035, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows3721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3721 = true := by
  decide +kernel

theorem tot3721 : totK PD2M8K2 D2M8K2.t3721 = [0, 205327023353, 486465725951, 201774642869, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows3722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3722 = true := by
  decide +kernel

theorem tot3722 : totK PD2M8K2 D2M8K2.t3722 = [70374419022, 261543122576, 375088916374, 176566347247, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows3723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3723 = true := by
  decide +kernel

theorem tot3723 : totK PD2M8K2 D2M8K2.t3723 = [173596593704, 445694724845, 276878197777, 28999859404, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
