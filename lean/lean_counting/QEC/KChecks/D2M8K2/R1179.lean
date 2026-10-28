import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4716 = true := by
  decide +kernel

theorem tot4716 : totK PD2M8K2 D2M8K2.t4716 = [0, 0, 0, 192335466568, 509748088789, 171966805007, 3622693787, 0] := by
  decide +kernel

theorem rows4717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4717 = true := by
  decide +kernel

theorem tot4717 : totK PD2M8K2 D2M8K2.t4717 = [0, 192215718355, 430449928107, 160486983653, 40714134734, 52225619984, 5679676912, 0] := by
  decide +kernel

theorem rows4718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4718 = true := by
  decide +kernel

theorem tot4718 : totK PD2M8K2 D2M8K2.t4718 = [0, 186000341653, 463004426570, 222033434649, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows4719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4719 = true := by
  decide +kernel

theorem tot4719 : totK PD2M8K2 D2M8K2.t4719 = [0, 19348689120, 301104845051, 470292573398, 91522343776, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
