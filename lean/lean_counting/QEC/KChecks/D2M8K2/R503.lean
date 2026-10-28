import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2012 = true := by
  decide +kernel

theorem tot2012 : totK PD2M8K2 D2M8K2.t2012 = [0, 104296678417, 430343656020, 346664107195, 30182052330, 0, 0, 0] := by
  decide +kernel

theorem rows2013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2013 = true := by
  decide +kernel

theorem tot2013 : totK PD2M8K2 D2M8K2.t2013 = [0, 0, 213316253422, 487049974174, 186510852689, 9668735432, 0, 0] := by
  decide +kernel

theorem rows2014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2014 = true := by
  decide +kernel

theorem tot2014 : totK PD2M8K2 D2M8K2.t2014 = [0, 84422589187, 317809617239, 376156123602, 103174943129, 3581949829, 0, 0] := by
  decide +kernel

theorem rows2015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2015 = true := by
  decide +kernel

theorem tot2015 : totK PD2M8K2 D2M8K2.t2015 = [0, 151208668935, 426741011592, 272837169529, 28132659300, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
