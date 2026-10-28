import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8780 = true := by
  decide +kernel

theorem tot8780 : totK PD2M8K2 D2M8K2.t8780 = [0, 77829559297, 276812468559, 369340661902, 137554424413, 10740121073, 0, 0] := by
  decide +kernel

theorem rows8781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8781 = true := by
  decide +kernel

theorem tot8781 : totK PD2M8K2 D2M8K2.t8781 = [0, 180336723352, 461873848302, 253157495808, 23046987921, 0, 0, 0] := by
  decide +kernel

theorem rows8782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8782 = true := by
  decide +kernel

theorem tot8782 : totK PD2M8K2 D2M8K2.t8782 = [0, 157470194010, 460956608811, 266772049349, 17496124833, 0, 0, 0] := by
  decide +kernel

theorem rows8783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8783 = true := by
  decide +kernel

theorem tot8783 : totK PD2M8K2 D2M8K2.t8783 = [0, 0, 255847685593, 489006568418, 134994122709, 2348440009, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
