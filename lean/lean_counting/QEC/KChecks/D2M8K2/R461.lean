import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1844 = true := by
  decide +kernel

theorem tot1844 : totK PD2M8K2 D2M8K2.t1844 = [0, 0, 170680683143, 478140512297, 224333181990, 6527009437, 0, 0] := by
  decide +kernel

theorem rows1845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1845 = true := by
  decide +kernel

theorem tot1845 : totK PD2M8K2 D2M8K2.t1845 = [0, 157317981048, 367196606211, 266724830638, 103025130088, 5371445965, 0, 0] := by
  decide +kernel

theorem rows1846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1846 = true := by
  decide +kernel

theorem tot1846 : totK PD2M8K2 D2M8K2.t1846 = [0, 166798042784, 445059685191, 281622508848, 29662355562, 0, 0, 0] := by
  decide +kernel

theorem rows1847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1847 = true := by
  decide +kernel

theorem tot1847 : totK PD2M8K2 D2M8K2.t1847 = [0, 121787798155, 443788866830, 313875761603, 25610119113, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
