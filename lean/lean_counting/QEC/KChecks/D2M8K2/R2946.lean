import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11784 = true := by
  decide +kernel

theorem tot11784 : totK PD2M8K2 D2M8K2.t11784 = [0, 190355134658, 469600832717, 227755425102, 13912140804, 0, 0, 0] := by
  decide +kernel

theorem rows11785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11785 = true := by
  decide +kernel

theorem tot11785 : totK PD2M8K2 D2M8K2.t11785 = [0, 86164502199, 386842380837, 356772605575, 69779761375, 6124536247, 0, 0] := by
  decide +kernel

theorem rows11786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11786 = true := by
  decide +kernel

theorem tot11786 : totK PD2M8K2 D2M8K2.t11786 = [0, 0, 207476324907, 465478806192, 215735744579, 12442493435, 0, 0] := by
  decide +kernel

theorem rows11787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11787 = true := by
  decide +kernel

theorem tot11787 : totK PD2M8K2 D2M8K2.t11787 = [0, 86563879224, 254520054565, 383640453025, 158350528934, 5521894595, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
